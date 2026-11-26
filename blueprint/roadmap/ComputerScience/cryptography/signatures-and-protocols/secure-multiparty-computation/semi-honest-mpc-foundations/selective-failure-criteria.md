# Selective failure attacks and immunity criteria

(i) *Slot selection:* if on secret $w$ the honest execution maps a reconstruction function over a context in which the response at a position selected by $w$ can be replaced, then corrupting that response yields a deterministic selective failure attack revealing whether $w$ selects it. (ii) *Nonlinear threshold:* for a Boolean-output protocol whose reconstruction tests whether a field-valued expression in $w$ equals $1$, an additive shift of one response yields an attack that fails exactly on a nontrivial set of secrets. (iii) *Passive-view factorization:* if for every deviation the failure game is the pushforward of the honest party's passive view under a fixed map, the protocol is selective-failure free, so passive privacy implies immunity. Applied to private information retrieval, one-bit XOR-sum reconstruction schemes are immune, while matrix-balanced schemes that reconstruct from a selected row are not, whenever there are a server, a column and two distinct rows.

## Proof sketch

In (i) and (ii) compute the failure probability for each secret directly; in (iii) the failure event is measurable with respect to the passive view, whose law does not depend on $w$.

## Depends on

- [Selective failure attacks](selective-failure-attacks.md)

## Sources

- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
