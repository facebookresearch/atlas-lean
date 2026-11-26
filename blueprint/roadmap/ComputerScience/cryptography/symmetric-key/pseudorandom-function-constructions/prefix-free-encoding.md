# Prefix-free encoding of messages

A *prefix-free encoding* is an injective map $\mathrm{pf} : M \to X^{\le \ell}$ into block sequences such that no image is a proper prefix of another, so the image of $\mathrm{pf}$ is a prefix-free set. Example: prepending the block count.

## Sources

- M. Bellare, R. Canetti and H. Krawczyk, "Pseudorandom Functions Revisited: The Cascade Construction and its Concrete Security", Proceedings of the 37th Annual Symposium on Foundations of Computer Science (FOCS 1996), IEEE, 1996, pp. 514–523, Section 3 ("Prefix-freeness": inputs encoded to form a prefix-free set, for example by prepending the length) and Section 4.
