# Markov bases give global convergence to the maximum likelihood estimate

Let $A \in \mathbb{Z}^{d\times m}$ with $\mathbb{1} \in \operatorname{row}(A)$, $c \in \mathbb{R}^m_{>0}$, and let $G_{\Lambda,c}$ be the detailed-balanced mass-action system built from a finite spanning set $\Lambda \subseteq \ker_{\mathbb{Z}}(A)$, with reactions $\gamma^- \rightleftharpoons \gamma^+$ and rate constants $c^{\gamma^+}, c^{\gamma^-}$ for $\gamma \in \Lambda$, whose positive steady states form the scaled toric variety $\mathcal{X}_{A,c}$. A finite $\Lambda \subseteq \ker_{\mathbb{Z}}(A)$ is a *Markov basis* if the binomials $x^{\gamma^+} - x^{\gamma^-}$, $\gamma \in \Lambda$, generate the toric ideal of $A$. A network *lacks relevant boundary steady states* if no stoichiometric compatibility class that meets the positive orthant contains a steady state on the boundary of the nonnegative orthant.

**Theorem.**

1. If $G_{\Lambda,c}$ lacks relevant boundary steady states, then for every data vector $u \in \mathbb{R}^m_{\ge 0}$ with $(\bar u + \ker A)_{>0} \ne \emptyset$, $\bar u = u/u_+$, the trajectory of $G_{\Lambda,c}$ started at $\bar u$ (even if $\bar u$ has zero entries) converges to the maximum likelihood estimate of $u$ in the log-affine model $\mathcal{M}_{A,c}$.
2. If $\Lambda$ is a Markov basis of $A$, then $G_{\Lambda,c}$ lacks relevant boundary steady states; hence the reaction network started at the normalized data always converges to the MLE.
3. If in addition $\Lambda$ is a vector-space basis of $\ker(A)$, then $G_\Lambda$ has deficiency zero; when it also lacks relevant boundary steady states for all rate constants, it has a unique globally stable positive steady state in each compatibility class.

An arbitrary spanning set is not enough: for $A = \begin{pmatrix} 4 & 2 & 3 & 1 \\ 0 & 2 & 1 & 3\end{pmatrix}$ some spanning sets, including a $\mathbb{Z}$-basis of $\ker_{\mathbb{Z}}(A)$, produce networks with relevant boundary steady states, so the integer-basis assumption alone does not give global convergence.

## Depends on

- [Maximum likelihood estimation of log-affine models by detailed-balanced reaction networks](mle-of-log-affine-models-by-detailed-balanced-reaction-networks.md)
- [Deficiency-zero theorem, weakly reversible case](../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium.md)

## Expansion

For detailed-balanced systems every $\omega$-limit set consists either of boundary steady states or of the unique positive steady state of the class (Siegel-MacLean), and all nonnegative steady states are detailed balanced. So the only obstruction to global convergence is a boundary point $x \ge 0$ satisfying the binomial equations $c^{\gamma^+} x^{\gamma^-} = c^{\gamma^-} x^{\gamma^+}$ for all $\gamma \in \Lambda$ inside a relevant class. When $\Lambda$ is a Markov basis these binomials cut out the closure of $\mathcal{X}_{A,c}$ in the nonnegative orthant, and Birch's theorem says this closure meets the class $(\bar u + \ker A)$ only in the positive MLE, so no relevant boundary steady state exists.

## Sources

- Oskar Henriksson, Carlos Améndola, Jose Israel Rodriguez, Polly Y. Yu, "Maximum likelihood estimation of log-affine models using detailed-balanced reaction networks", *Journal of Mathematical Biology* 91(4) (2025), 34, Definition 2.2, Lemma 2.3, Propositions 3.8, 3.12 and 3.13, Theorems 5.1, 5.2 and 5.5, Corollary 5.6, Example 5.4, <https://doi.org/10.1007/s00285-025-02262-5> (preprint arXiv:2411.07986).
