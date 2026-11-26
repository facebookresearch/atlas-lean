# Discrete moment duality of the de Finetti process and the block-counting chain

**Setting.** Let $L$ be a label-forgetful random ancestry mapping on $\mathbb N$ (see the depended-on article) and let $L_1,L_2,\dots$ be i.i.d. copies of $L$. Start from an exchangeable $\{0,1\}$-valued sequence $(X_0(i))_{i\ge1}$ with $\mathbb P(X_0(i)=1)=x\in(0,1)$, independent of the $L_k$, and set

$$X_k(i)=\inf_{j\in L_k(i)}X_{k-1}(j),\qquad k\ge1 .$$

Every generation $(X_k(i))_{i\ge1}$ is exchangeable, so by de Finetti's theorem the limit

$$\Theta_k=\lim_{p\to\infty}\frac1p\sum_{i=1}^p X_k(i)\in[0,1]$$

exists almost surely, and given $\Theta_k$ the $X_k(i)$ are i.i.d. Bernoulli$(\Theta_k)$. The sequence $(\Theta_k)_{k\ge0}$ is a $[0,1]$-valued Markov chain, the **de Finetti process**. The **block-counting chain** $(A_k)_{k\ge0}$ is the $\mathbb N$-valued Markov chain with

$$\mathbb P(A_1=m\mid A_0=n)=\mathbb P\big(|L(\{1,\dots,n\})|=m\big),\qquad n,m\in\mathbb N,$$

which counts the potential ancestors of a sample of size $n$, $k$ generations back.

**Theorem (moment duality).** For all $x\in[0,1]$ and $n,k\in\mathbb N$,

$$\mathbb E_x\big[\Theta_k^{\,n}\big]=\mathbb E_n\big[x^{A_k}\big].$$

**Proposition (approximation of continuous-time processes).** Let $L^N$ be label-forgetful mappings with block-counting chains $A^N$ and dual de Finetti processes $\Theta^N$. Suppose there are a continuous-time $\mathbb N$-valued Markov process $(A_t)$ that is moment dual to a $[0,1]$-valued Feller process $(W_t)$, and a sequence $a_N\to\infty$ such that $A^N_{\lfloor a_N t\rfloor}\Rightarrow A_t$ for each fixed $t\in[0,T]$ whenever $A^N_0=A_0$. Then $W^N_t:=\Theta^N_{\lfloor a_N t\rfloor}$ converges weakly to $W$ in $D([0,T],[0,1])$.

## Expansion

The duality is a sampling identity. The probability that the first $n$ individuals of generation $k$ all carry type $1$ equals $\mathbb E_x[\Theta_k^n]$ by conditional independence given $\Theta_k$. On the other hand, these individuals all have type $1$ exactly when all of their potential ancestors in generation $0$ do; by label-forgetfulness the number of such ancestors has the law of $A_k$ started from $n$, and given that number $m$ the probability that $m$ generation-$0$ individuals all have type $1$ is $x^m$. Summing over $m$ gives $\mathbb E_n[x^{A_k}]$. The same computation with $k=1$ shows that the conditional moments of $\Theta_{k+1}$ given the past depend only on $\Theta_k$, which is the Markov property.

For the approximation result, duality converts convergence in law of $A^N$ into pointwise convergence of $\mathbb E_x[(W^N_t)^p]$ to $\mathbb E_x[W_t^p]$ for every monomial; uniformity in $x$ and density of polynomials in $C([0,1])$ give strong convergence of the semigroups, and standard semigroup convergence theorems for Feller processes yield convergence in $D([0,T],[0,1])$. Lookdown constructions of $\Xi$-coalescents with branching, and of Wright–Fisher diffusions with selection, arise this way as limits of discrete label-forgetful mappings.

## Depends on

- [Label-forgetfulness characterizes propagation of exchangeability](label-forgetfulness-characterizes-propagation-of-exchangeability.md)
- [Dual moment polynomial of Kingman's coalescent](../../population-genetics/diffusion-theory/wright-fisher-semigroup-and-moment-duality/dual-moment-poly.md)

## Sources

- Adrián González Casanova, Ariel Offenstadt and Arno Siri-Jégousse, "Moment duality and propagation of exchangeability", arXiv:2606.28174 (2026), Section 2.2, Theorem 2.5 and Proposition 2.7; Section 3, Theorems 3.1 and 3.4. <https://doi.org/10.48550/arXiv.2606.28174>
