# A prefix-free PRF composed with a prefix-free encoding is a variable-length PRF

If $F$ is a prefix-free PRF on $X^{\le \ell}$ and $\mathrm{pf} : M \to X^{\le \ell}$ is an efficiently computable prefix-free encoding, then $F'(k, m) = F(k, \mathrm{pf}(m))$ is a PRF on $M$ against arbitrary (not necessarily prefix-free) adversaries.

## Proof sketch

Any adversary for $F'$ becomes a prefix-free adversary for $F$ by encoding its queries, since encodings of distinct messages are never prefixes of one another; repeated messages are answered consistently.

## Depends on

- [Prefix-free encoding of messages](prefix-free-encoding.md)
- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)

## Sources

- M. Bellare, R. Canetti and H. Krawczyk, "Pseudorandom Functions Revisited: The Cascade Construction and its Concrete Security", Proceedings of the 37th Annual Symposium on Foundations of Computer Science (FOCS 1996), IEEE, 1996, pp. 514–523, Section 3 ("Prefix-freeness": pseudorandomness against prefix-free distinguishers implies that any prefix-free encoding suffices against arbitrary distinguishers).
