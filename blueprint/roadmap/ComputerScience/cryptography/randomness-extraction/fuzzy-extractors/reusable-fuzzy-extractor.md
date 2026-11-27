# Reusable fuzzy extractor

A fuzzy extractor is *reusable* if its key $r^*$ from an enrollment $\mathrm{Gen}(w^*)$ remains indistinguishable from uniform even when the adversary sees the helpers (and, for *strong* reusability, also the keys) of further enrollments $\mathrm{Gen}(w^* + \delta_i)$ on correlated readings with adversarially chosen bounded perturbations $\delta_i$, possibly in a public-parameters model. *Weak* reusability withholds the other keys.

## Depends on

- [Fuzzy extractor and secure sketch](fuzzy-extractor.md)

## Sources

- D. Apon, C. Cho, K. Eldefrawy and J. Katz, "Efficient, Reusable Fuzzy Extractors from LWE", Cyber Security Cryptography and Machine Learning (CSCML 2017), LNCS 10332, 2017.
