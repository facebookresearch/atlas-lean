# Limits of rescaled Markov chains solve the limit martingale problem

Let $E$ be a compact metric space, $T>0$, and $A$ a set of pairs $(f,Af)$ with $f,Af\in C(E)$. Let $\mathcal G\subseteq A$ be a countable set such that every pair of $A$ is the bounded-pointwise limit of a sequence in $\mathcal G$, as in [the countable core lemma](countable-bounded-pointwise-graph-core-for-marti.md). For each $N$ let $(Y^N_k)_{k\ge0}$ be a Markov chain on $E_N\subseteq E$ with transition operator $P_N$, let $M_N\to\infty$, and put

$$X^N_t=Y^N_{\lfloor tM_N\rfloor},\qquad A_Nf=M_N\,(P_Nf-f)\ \text{ on }E_N .$$

Assume

1. $\sup_{x\in E_N}|A_Nf(x)-Af(x)|\to0$ for every $(f,Af)\in\mathcal G$;
2. $X^N_0\Rightarrow\mu$;
3. the laws of $X^N$ are C-tight in $D([0,T],E)$.

Then every subsequential limit in law $X$ of $(X^N)$ has continuous paths and solves the $(A,\mu)$ [martingale problem](martingale-problems-generic-definition.md) on $[0,T]$ with respect to its natural filtration. Uniqueness for the limit problem is a separate hypothesis; with it, the [diffusion-approximation theorem](diffusion-approximation-framework-process-level.md) gives convergence of the whole sequence.

## Depends on

- [A countable bounded-pointwise core of the graph suffices for a martingale problem](countable-bounded-pointwise-graph-core-for-marti.md)
- [Martingale problems](martingale-problems-generic-definition.md)
- [C-tightness: tight laws with vanishing maximal jumps have continuous limit points](../../convergence-of-measures/skorokhod-space/c-tightness-criterion.md)

## Proof depends on

- [Diffusion approximation: tightness and a well-posed limit martingale problem give process-level convergence](diffusion-approximation-framework-process-level.md)
- [Dynkin martingale of a discrete-time Markov chain](../markov-and-strong-markov-properties/dynkin-martingale-of-a-discrete-time-markov-chai.md)
- [Borel sigma-algebra of D equals the coordinate sigma-algebra; fdd determine laws](../../convergence-of-measures/skorokhod-space/borel-sigma-algebra-of-d-equals-the-coordinate-s.md)

## Expansion

A full proof page must establish:

- For each $(f,Af)\in\mathcal G$, the [Dynkin martingale of the chain](../markov-and-strong-markov-properties/dynkin-martingale-of-a-discrete-time-markov-chai.md) gives, for $0\le t_1<\cdots<t_r\le s\le t\le T$ and bounded continuous $H$,

    $$\mathbb E\Bigl[\Bigl(f(X^N_t)-f(X^N_s)-\int_s^tA_Nf(X^N_u)\,du\Bigr)H(X^N_{t_1},\ldots,X^N_{t_r})\Bigr]\to0,$$

    the error from the grid being at most $2\sup|A_Nf|/M_N$.
- Replacing $A_Nf$ by $Af$ by hypothesis 1, and passing to the limit along the subsequence: continuity of the limit paths makes the evaluation and time-integral functionals continuous at the limit.
- A monotone-class argument from the cylinder functions $H$ to the natural filtration, and the extension from $\mathcal G$ to all of $A$ by the countable core lemma.
- Application to Wright–Fisher chains with selection, which constructs a solution of the selection Wright–Fisher martingale problem (compare the [existence of the selection-mutation Wright–Fisher diffusion](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/existence-of-the-selection-mutation-wf-diffusion.md)).

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4 (existence of solutions by approximation).
