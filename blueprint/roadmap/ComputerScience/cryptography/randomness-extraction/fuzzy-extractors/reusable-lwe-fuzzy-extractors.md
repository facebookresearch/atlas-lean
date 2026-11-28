# Reusability of LWE-based fuzzy extractors

(a) If all enrollments of the LWE fuzzy extractor share one public random matrix $A$, the scheme is weakly reusable whenever it is a secure fuzzy extractor. (b) In the encryption-based variant (Apon, Cho, Eldefrawy and Katz, Section 5), all enrollments share a public uniform matrix $A \in \mathbb{Z}_q^{m \times n}$; $\mathrm{Gen}(w)$ picks a uniform $s \in \mathbb{Z}_q^n$, sets $c = As + w$, picks a uniform key $r \in \{0,1\}^m$ and publishes $(c, B, h)$ with $h = Bs + e + (q/2)\,r$ (with $q/2$ rounded to an integer) for a fresh uniform $B \in \mathbb{Z}_q^{m \times n}$ and a fresh error vector $e \in \mathbb{Z}_q^m$, so the reading is the LWE noise of an encoding of $s$, and $s$ encrypts $r$; $\mathrm{Rep}$ decodes $s$ from $c - w'$ and decrypts $r$ coordinatewise. Suppose that each coordinate of the reading $w$ is drawn independently from an error law $\chi$ on $\mathbb{Z}_q$, that the coordinates of $e$ are drawn from the same $\chi$, and that $\mathrm{LWE}_{n,(Q+2)m,q,\chi}$ is hard. Then the scheme is strongly reusable against adversaries making at most $Q$ enrollment queries. Without the link between the law of $w$ and $\chi$ the claim fails: for a point-mass reading $w$, $c - w = As$ reveals $s$ and hence $r$.

## Proof sketch

With a common matrix, helpers for perturbed readings $A s_i + w^* + \delta_i$ are computable from a single LWE sample for $w^*$ by shifting with $A(s_i - s^*)$ and $\delta_i$, so extra enrollments give the adversary nothing new. For (b), the challenge enrollment and the $Q$ further ones are simulated from $Q + 2$ batches of $m$ LWE samples $(B_i, B_i s + e_i)$ with one secret $s$, namely $(Q+2)m$ samples, which are replaced by uniform in one step; then $r$ is masked by a uniform vector.

## Depends on

- [Reusable fuzzy extractor](reusable-fuzzy-extractor.md)
- [Learning with errors](../../public-key/hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [A computational fuzzy extractor from LWE (decode-then-extract)](lwe-fuzzy-extractor.md)

## Sources

- D. Apon, C. Cho, K. Eldefrawy and J. Katz, "Efficient, Reusable Fuzzy Extractors from LWE", Cyber Security Cryptography and Machine Learning (CSCML 2017), LNCS 10332, 2017, Theorem 1 and Section 5.
- B. Fuller, X. Meng and L. Reyzin, "Computational Fuzzy Extractors", Information and Computation 275, 2020.
