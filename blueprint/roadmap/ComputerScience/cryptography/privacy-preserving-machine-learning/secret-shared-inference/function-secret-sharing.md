# Function secret sharing and distributed point functions

An $m$-party *function secret sharing* (FSS) scheme for a function family splits a description of $f:\{0,1\}^n\to\mathbb{G}$ into keys $k_1,\dots,k_m$ with $\sum_i\mathrm{Eval}(i,k_i,x)=f(x)$ for every $x$, while any $t$ of the keys can be simulated from the permitted leakage. A *distributed point function* (DPF) is FSS for point functions.

A *function family* is $\mathcal{F}=(P_{\mathcal{F}},E_{\mathcal{F}})$: a set $P_{\mathcal{F}}$ of descriptions $\hat f$, each specifying an input length $n\ge1$, a finite Abelian group $\mathbb{G}$ given as a product of cyclic groups, and a size, and a polynomial-time interpreter $E_{\mathcal{F}}$ computing $f(x)$ from $(\hat f,x)$. An FSS scheme is $(\mathrm{Gen},\mathrm{Eval})$: $\mathrm{Gen}(1^\lambda,\hat f)$ is PPT and outputs $(k_1,\dots,k_m)$; $\mathrm{Eval}(i,k_i,x)$ is polynomial time and outputs $y_i\in\mathbb{G}$. For a leakage function $\mathrm{Leak}$ and $1\le t<m$ it is an *$m$-party $t$-secure FSS for $\mathcal{F}$* if

- *correctness:* for all $\hat f\in P_{\mathcal{F}}$ describing $f$ and all $x\in\{0,1\}^n$, $\Pr[\sum_{i=1}^m\mathrm{Eval}(i,k_i,x)=f(x)]=1$ over $(k_1,\dots,k_m)\leftarrow\mathrm{Gen}(1^\lambda,\hat f)$;
- *secrecy:* for every $S\subset[m]$ with $|S|=t$ there is a PPT simulator $\mathrm{Sim}$ such that for every sequence $(\hat f_\lambda)$ of polynomial-size descriptions from $P_{\mathcal{F}}$, the outputs $(k_i)_{i\in S}$ of $\mathrm{Gen}(1^\lambda,\hat f_\lambda)$ and $\mathrm{Sim}(1^\lambda,\mathrm{Leak}(\hat f_\lambda))$ are computationally indistinguishable.

By default $t=m-1$ and $\mathrm{Leak}(\hat f)=(1^n,\text{size},\mathbb{G})$; the two-party *subtractive* variant requires $\mathrm{Eval}(1,k_1,x)-\mathrm{Eval}(2,k_2,x)=f(x)$. The point function $f_{\alpha,\beta}$ ($\alpha\in\{0,1\}^n$, $\beta\in\mathbb{G}$) maps $\alpha$ to $\beta$ and every other input to $0$; a DPF is an FSS for all point functions with $\mathrm{Leak}(\hat f)=(1^n,\mathbb{G})$.

## Depends on

- [Computational indistinguishability of distribution ensembles](../../security-games/computational-indistinguishability-of-ensembles/computational-indistinguishability-of-ensembles.md)

## Proof depends on

None.

## Expansion

A definition. Its first construction result is the [PRG-based two-party DPF](tree-based-distributed-point-function.md).

## Sources

- Elette Boyle, Niv Gilboa, Yuval Ishai, "Function Secret Sharing: Improvements and Extensions", ACM CCS 2016, DOI 10.1145/2976749.2978429; numbers from the full version, IACR ePrint 2018/707: pp. 5–6, Definitions 2.1, 2.2 and 2.3 of the full version (author-hosted copy).
