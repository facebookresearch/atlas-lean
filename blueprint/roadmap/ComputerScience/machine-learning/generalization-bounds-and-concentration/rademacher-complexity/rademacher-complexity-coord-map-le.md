# The contraction lemma

Let $A \subseteq \mathbb{R}^n$ be bounded and let $\varphi_1, \dots, \varphi_n : \mathbb{R} \to \mathbb{R}$ be $L$-Lipschitz. Then

$$R\big(\{(\varphi_1(a_1), \dots, \varphi_n(a_n)) : a \in A\}\big) \le L\, R(A).$$

No condition $\varphi_i(0) = 0$ is needed in this convention; this is exactly the form of Shalev-Shwartz and Ben-David's Lemma 26.9. The absolute-value versions assume $\varphi_i(0) = 0$: Bartlett and Mendelson's Theorem 12.4 pays a factor $2$, and Ledoux and Talagrand's comparison principle for contractions (§4.5) is stated with an absolute value for contractions vanishing at $0$. The proof replaces one coordinate map at a time by $x \mapsto L x$: pairing each sign vector with the one that differs at that coordinate, the sum of the two suprema can only grow (Shalev-Shwartz and Ben-David's proof of Lemma 26.9). With the margin loss this is the step from the complexity of a real-valued class to that of its ramp-loss class in margin bounds.

## Informally uses

- [Scaling](rademacher-complexity-smul.md): builds on, to identify the complexity of $\{L a : a \in A\}$ with $L\, R(A)$.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Lemma 26.9.
- P. L. Bartlett and S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and structural results*, Journal of Machine Learning Research 3 (2002) 463–482, <https://jmlr.csail.mit.edu/papers/volume3/bartlett02a/bartlett02a.pdf>, Theorem 12, part 4 (the absolute-value version).
- cf. M. Ledoux and M. Talagrand, *Probability in Banach Spaces*, Springer (1991), Section 4.5 (the comparison principle for contractions, in the absolute-value form and assuming $\varphi_i(0) = 0$).
