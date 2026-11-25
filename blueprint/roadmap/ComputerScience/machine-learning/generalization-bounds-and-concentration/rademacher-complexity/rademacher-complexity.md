# Empirical Rademacher complexity

For $A \subseteq \mathbb{R}^n$,

$$R(A) = \frac{1}{n}\, \frac{1}{2^n} \sum_{\sigma \in \{-1, 1\}^n} \sup_{a \in A} \sum_{i=1}^n \sigma_i a_i ,$$

the expectation over independent uniform signs written as a finite average. When $A = \{(f(x_1), \dots, f(x_n)) : f \in \mathcal{F}\}$ is the set of value vectors of a function class on a fixed sample, $R(A)$ is the empirical Rademacher complexity of $\mathcal{F}$ on that sample.

This is the convention of Shalev-Shwartz and Ben-David (Section 26.1, equation (26.5)) and of Bartlett, Foster and Telgarsky. Bartlett and Mendelson (2002) use $\mathbb{E} \sup_a \lvert \frac{2}{n} \sum_i \sigma_i a_i \rvert$ instead; the two agree up to the factor $2$ when $A$ is symmetric ($A = -A$). In the convention here, several of their structural inequalities become identities, because each sign has mean zero.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Section 26.1, equation (26.5).
- P. L. Bartlett and S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and structural results*, Journal of Machine Learning Research 3 (2002) 463–482, <https://jmlr.csail.mit.edu/papers/volume3/bartlett02a/bartlett02a.pdf>, Definition 2 (their $R_n$, with the absolute value and the factor $2$).
