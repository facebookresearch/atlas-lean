# Semantic security with error $\varepsilon$

A public-key encryption scheme, with a length function on its messages and a distribution of the
adversary's coins, is semantically secure with error $\varepsilon$ (for a priori information in a type
$H$ and guesses in a type $T$) if for every adversary $A$ there is an ideal adversary $A'$ such that
for every plaintext distribution $X$, every function $h$ and every target function $f$, the
probability that $A$ wins the [real experiment](ss-real.md) is at most $\varepsilon$ more than the
probability that $A'$ wins the [ideal experiment](ss-ideal.md).

The quantifiers are in Goldreich's order: $A'$ may depend on $A$ but not on $X$, $h$ or $f$. Unlike
Goldreich's definition, the real adversary $A$ is not given the length of the plaintext (only $A'$ is);
this weakens the definition slightly and is harmless when ciphertexts reveal the length. The
definition is concrete: one scheme, one error, and no complexity bound on $A$ or $A'$ (Goldreich
requires both to be probabilistic polynomial time). In this concrete model every function counts as an adversary, so no correct public-key scheme with two distinct messages of the same length meets it with $\varepsilon < \tfrac12$
([unattainability](not-semantically-secure-of-correct.md)); the per-adversary statements carry the
content for public-key schemes.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Definition 5.2.2.
- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all
  partial information", Proc. 14th ACM STOC (1982), 365-377, Section 1 (security as the impossibility
  of obtaining partial information from the ciphertext).
