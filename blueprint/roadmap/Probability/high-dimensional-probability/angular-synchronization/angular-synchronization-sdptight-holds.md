# The semidefinite relaxation is tight up to the noise level √(n / log n)

In angular synchronization one observes $C = zz^* + \sigma W$, where $z \in \mathbb C^n$ has entries of modulus $1$, $\sigma \ge 0$, and $W$ is Hermitian with zero diagonal and independent entries $W_{kl}$, $k < l$, whose real and imaginary parts are independent $N(0, 1/2)$. Problem (P) maximizes $x^*Cx$ over vectors $x$ with $|x_k| = 1$; its maximizer is compared with others up to a global phase $e^{i\theta}$. The semidefinite relaxation maximizes $\operatorname{Re}\operatorname{tr}(CX)$ over Hermitian positive semidefinite $X$ with $X_{kk} = 1$; it is tight on $C$ if for some maximizer $\hat x$ of (P), unique up to phase, $\hat x\hat x^*$ is its unique maximizer. There is $c > 0$ such that whenever $0 \le \sigma_n \le c\sqrt{n/\log n}$ for all $n$, for any signals $z_n$, the outer probability that the relaxation is not tight tends to $0$. Zhong and Boumal (2018) proved this, answering Bandeira's Open Problem 10.2.

## Sources

- Problem: A. S. Bandeira, Ten Lectures and Forty-Two Open Problems in the Mathematics of Data Science (2015-2016), Section 10.2, Open Problem 10.2, https://afonsobandeira.wordpress.com/2015/12/09/42l10psynchronization/.
- Resolution: Y. Zhong and N. Boumal, Near-optimal bounds for phase synchronization, SIAM J. Optim. 28 (2018), 989-1016; arXiv:1703.06605, https://doi.org/10.1137/17M1122025.
