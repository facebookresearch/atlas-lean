# Reusability of LWE-based fuzzy extractors

(a) If all enrollments of the LWE fuzzy extractor share one public random matrix $A$, the scheme is weakly reusable whenever it is a secure fuzzy extractor. (b) The encryption-based variant, which uses the reading as the noise of LWE encryptions of the key under fresh public randomness, is strongly reusable against adversaries making at most $t$ enrollment queries, assuming hardness of LWE with $(t+2)m$ samples.

## Proof sketch

With a common matrix, helpers for perturbed readings $A s_i + w^* + \delta_i$ are computable from a single LWE sample for $w^*$ by shifting with $A(s_i - s^*)$ and $\delta_i$, so extra enrollments give the adversary nothing new. For (b), all enrollments together form an LWE instance with $(t+2)m$ samples, which is replaced by uniform in one step.

## Depends on

- [Reusable fuzzy extractor](reusable-fuzzy-extractor.md)
- [Learning with errors](../../public-key/hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [A computational fuzzy extractor from LWE (decode-then-extract)](lwe-fuzzy-extractor.md)

## Sources

- D. Apon, C. Cho, K. Eldefrawy and J. Katz, "Efficient, Reusable Fuzzy Extractors from LWE", Cyber Security Cryptography and Machine Learning (CSCML 2017), LNCS 10332, 2017.
- B. Fuller, X. Meng and L. Reyzin, "Computational Fuzzy Extractors", Information and Computation 275, 2020.
