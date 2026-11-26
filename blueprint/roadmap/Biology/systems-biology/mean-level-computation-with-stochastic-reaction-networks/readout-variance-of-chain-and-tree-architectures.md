# Readout variance of chain and tree architectures for stochastic chemical arithmetic

Compose the stochastic identification ($A\to A+X$, $X\to\emptyset$, unit rates), addition and multiplication modules, whose outputs are correct at the level of stationary means. With mean-level computation the output must be estimated by Monte Carlo averaging, so its stationary variance and autocovariance set the readout cost.

**Identification chains.** For a chain $A_0\to A_1\to\dots\to A_n$ of identification modules with source mean $a$,
$$\operatorname{Cov}_\pi(A_n(0),A_n(t))=a\,e^{-t}\sum_{j=0}^n\sum_{k=0}^j\frac{\binom{j+k}{k}}{2^{j+k}(j-k)!}t^{j-k},\qquad \operatorname{Var}_\pi A_n=a\,(2n+1)\frac{\binom{2n}{n}}{4^n}\sim\frac{2}{\sqrt\pi}\sqrt n\;a .$$
Each stage adds Poisson noise and passes on smoothed upstream noise, so the Fano factor grows like $\sqrt n$, and the mean convergence time grows at most linearly in $n$.

**Addition of $n$ inputs.** A balanced binary tree ($n=2^m$) is strongly lumpable to an identification chain of length $m=\log_2n$ driven by the total input, so
$$\operatorname{Var}_\pi(\text{output})=s\,(2m+1)\frac{\binom{2m}{m}}{4^m}\sim\frac{2}{\sqrt\pi}\sqrt{\log_2n}\;s,\qquad s=\sum_ia_i .$$
A linear chain sums rows that are identification chains of lengths $\ell_i$, giving $\operatorname{Var}_\pi(S_n)=\sum_ia_i(2\ell_i+1)\binom{2\ell_i}{\ell_i}4^{-\ell_i}$ and, for bounded input means, $\frac23a_{\min}n^{3/2}\le\operatorname{Var}_\pi(S_n)\le\sqrt2\,a_{\max}n^{3/2}$, i.e. a Fano factor of order $\sqrt n$. The tree is far better for addition.

**Multiplication of $n$ independent inputs of mean $a$ (computing $a^n$).** For the binary tree, for fixed $t$ there are $0<c_1\le c_2$ with
$$a^{2n-1}e^{c_1n}\le C(t)\le a^{2n-1}e^{c_2n}\ (a>1),\qquad e^{c_1n}\le C(t)\le e^{c_2n}\ (a=1),\qquad a^ne^{c_1n}\le C(t)\le a^ne^{c_2n}\ (0<a<1),$$
an exponential amplification relative to the squared mean $a^{2n}$. For the linear chain, $c_1a^{2n-1}\le C(t)\le c_2a^{2n-1}(1+\frac1{2a})^n$ for $a>1$, $c_1\le C(t)\le c_2(3/2)^n$ for $a=1$, $c_1a^n\le C(t)\le c_2a^n(a+\frac12)^n$ for $\frac12<a<1$, and $C(t)=\Theta(a^n)$ for $0<a<\frac12$. So for multiplication the tree can be exponentially worse than the chain, the opposite of addition.

## Depends on

- [Conditional Poisson representation of a randomly driven immigration-death process](conditional-poisson-representation-of-randomly-driven-immigration-death.md)

## Expansion

The stationary autocovariance obeys $C_{i+1}=a e^{-t}+\mathcal KC_i$ with $(\mathcal Kf)(t)=\frac12\int_0^\infty e^{-u}(f(t+u)+f(|t-u|))du$ (stationary covariance formula of the conditional Poisson representation); since $\mathcal K$ maps $e^{-t}t^r$ to combinations of $e^{-t}t^{q}$, the recursion is solved by the polynomial-times-exponential sums above, and $t=0$ gives the central-binomial variance. Strong lumpability (Ball-Yeo criterion) reduces trees and chains of adders to identification chains on level sums. For multiplication the output variance satisfies $\operatorname{Var}X\approx\mathbb E[AB]+\operatorname{Var}(AB)$-type recursions; squaring through $\log_2n$ levels of a tree compounds relative noise multiplicatively at every level, which explains the exponential factor, while a chain multiplies one fresh low-noise input per stage.

## Sources

- D. F. Anderson, S. Moon, "Mean-level arithmetic computation via stochastic reaction networks", arXiv:2611.11069 (2026), Section 6 (Theorems 6.1, 6.2, 6.4-6.10, 6.12-6.14, Lemmas 6.3 and 6.11), <https://doi.org/10.48550/arXiv.2611.11069>.
