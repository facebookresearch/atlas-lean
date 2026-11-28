# Selective failure attacks and immunity criteria

(i) *Slot selection:* if on secret $w$ the honest execution maps a reconstruction function over a context in which the response at a position selected by $w$ can be replaced, then corrupting that response yields a deterministic selective failure attack revealing whether $w$ selects it. (ii) *Nonlinear threshold:* for a Boolean-output protocol whose reconstruction tests whether a field-valued expression in $w$ equals $1$, an additive shift of one response yields an attack that fails exactly on a nontrivial set of secrets. (iii) *Passive-view factorization:* if for every deviation the failure event is a fixed function of the corrupted participants' view in the passive execution (and of the deviation's coins), the protocol is selective-failure free, and passive privacy, which makes the law of that view independent of $w$, implies immunity: the failure probability does not depend on $w$. Applied to private information retrieval, one-round schemes in which each server answers one bit and the user outputs the XOR of the answers (such as the two-server and subcube XOR schemes) are immune, since the change a deviating server causes in the XOR is determined by its deviating and its honest answer, both functions of its own view, while schemes balanced as a matrix, in which the user retrieves a column and reconstructs from the row selected by its index, are not, whenever there are a server, a column and two distinct rows: corrupting the answer for one row fails exactly when the queried row is that row, which is not a function of the server's view.

## Proof sketch

In (i) and (ii) compute the failure probability for each secret directly; in (iii) the failure event is measurable with respect to the corrupted participants' passive view, whose law does not depend on $w$ by passive privacy.

## Depends on

- [Selective failure attacks](selective-failure-attacks.md)
- [Private information retrieval schemes](../../private-information-retrieval/pir-schemes.md)
- [The two-server and subcube XOR PIR schemes](../../private-information-retrieval/subcube-pir-schemes.md)

## Sources

- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
