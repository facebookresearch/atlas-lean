# Semigroup convergence implies finite-dimensional convergence

Let $E$ be a compact metric space and $(T(t))_{t\ge0}$ a Feller semigroup on $C(E)$, with transition kernels $(K_t)$. For each $N$ let $(X^N_k)_{k\ge0}$ be a discrete-time Markov chain on $E$ with transition operator $T_Nf(x)=\mathbb E\bigl[f(X^N_{k+1})\mid X^N_k=x\bigr]$, and let $a_N\to\infty$. Assume that

- $T_N^{\lfloor a_Nt\rfloor}f\to T(t)f$ uniformly on $E$, locally uniformly in $t\ge0$, for every $f\in C(E)$;
- $X^N_0\to\mu$ in law.

Then for all $0\le t_1<\dots<t_k$ the law of $\bigl(X^N_{\lfloor a_Nt_1\rfloor},\dots,X^N_{\lfloor a_Nt_k\rfloor}\bigr)$ converges weakly to that of $(X_{t_1},\dots,X_{t_k})$, where $X$ is the Markov process with semigroup $(T(t))$ and initial law $\mu$, whose finite-dimensional laws are those of the [path-space measure](path-measure.md) integrated against $\mu$.

## Depends on

- [Path-space measure of a Markov semigroup](path-measure.md)

## Proof depends on

- [Trotter-Kurtz: chain semigroups converge to a limit semigroup](trotter-kurtz-chain-semigroups-converge-to-a-lim.md)

## Expansion

A proof page must establish, by induction on $k$, the convergence of $\mathbb E\prod_{i\le k}f_i\bigl(X^N_{\lfloor a_Nt_i\rfloor}\bigr)$ for $f_i\in C(E)$, using the Markov property at the time $\lfloor a_Nt_{k-1}\rfloor$; the number of steps $\lfloor a_Nt_k\rfloor-\lfloor a_Nt_{k-1}\rfloor$ equals $\lfloor a_Ns_N\rfloor$ for some $s_N\to t_k-t_{k-1}$, which is where local uniformity in $t$ and continuity of $t\mapsto T(t)f$ are used; convergence of products in $C(E)^{\otimes k}$ determines weak convergence on the compact space $E^k$. A test case is a finite-state chain with $T_N=I+a_N^{-1}Q$ for a rate matrix $Q$ (stochastic for large $N$), where $T_N^{\lfloor a_Nt\rfloor}\to e^{tQ}$ directly.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Chapter 4 (convergence of finite-dimensional distributions).
