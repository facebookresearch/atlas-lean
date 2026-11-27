# Bounded asynchronous session subtyping is undecidable

Asynchronous session subtyping stays undecidable when each anticipated output may pass only a bounded, but not fixed in advance, number of nested inputs; for each fixed bound the relation is decidable.

Let $\le$ now denote the asynchronous subtyping of the second source: the relation of [asynchronous subtyping](asynchronous-subtyping-of-binary-session-types.md) with one more condition in clause 2, namely that if $\mathcal{A} \ne [\,]^1$ then every continuation $T_i$ ($i \in I$) contains at least one input branching (no orphan messages). An input context is $\mathsf{k}$-bounded if its maximal number of nested inputs is at most $\mathsf{k}$. For $\mathsf{k} \ge 0$, $\le_{\mathsf{k}}$ is defined as $\le$ with the input context of clause 2 required to be $\mathsf{k}$-bounded; $\le_0$ is synchronous subtyping. $T$ is a bounded asynchronous subtype of $S$, $T \le_{\mathsf{bound}} S$, if $T \le_{\mathsf{k}} S$ for some $\mathsf{k}$.

**Theorem.** The following problem is undecidable. Input: two session types $T$ and $S$. Question: does $T \le_{\mathsf{bound}} S$ hold?

## Depends on

- [Asynchronous subtyping of binary session types](asynchronous-subtyping-of-binary-session-types.md)

## Proof depends on

None.

## Expansion

A queue machine $M$ is bound on input $x$ if there is $k$ such that every queue content reachable from $(s, x\#)$ has length at most $k$ (Definition 4.3). Deciding whether $M$ does not terminate and is bound on $x$ is undecidable (Lemma 4.4 of the source): boundedness is undecidable, since on bound machines termination is decided by exploring the finitely many reachable configurations, and boundedness reduces to bounded non-termination by adding a symbol that is re-enqueued whenever it is dequeued. With the queue-machine encoding of the [single-choice undecidability proof](asynchronous-single-choice-subtyping-undecidable.md), $[\![s]\!]^{\emptyset} \le_{\mathsf{bound}} [\![x\#]\!]$ holds if and only if $M$ does not terminate and is bound on $x$ (Theorem 4.5). For each fixed $\mathsf{k}$, $\le_{\mathsf{k}}$ is decided by the source's subtyping algorithm with $\mathsf{k}$-bounded input contexts (Section 3).

## Sources

- Mario Bravetti, Marco Carbone and Gianluigi Zavattaro, "On the boundary between decidability and undecidability of asynchronous session subtyping", *Theoretical Computer Science* 722, 19–51, 2018, <https://doi.org/10.1016/j.tcs.2018.02.010>; read as arXiv:1703.00659v3, <https://arxiv.org/abs/1703.00659v3>: Definitions 2.4 (asynchronous subtyping with the no orphan message constraint), 2.11 and 2.12 (bounded subtyping), Definition 4.3, Lemma 4.4, Theorem 4.5 and Corollary 4.6 of that version.
