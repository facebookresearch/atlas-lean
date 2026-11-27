# Moment invariant ideal of a probabilistic loop

The moment invariant ideal of order $\ell$ of a probabilistic polynomial loop is the set of all polynomials in the moments of degree at most $\ell$ of the program variables that vanish after every number of loop iterations. A basis of it is the strongest polynomial invariant among those moments.

**Probabilistic loops.** A probabilistic polynomial program over variables $\vec{x} = (x_1, \dots, x_k)$ has a set $Q$ of locations, an initial location $q_0$ and transitions $(q, f, pr, q')$ with $f \in \mathbb{Q}[x_1, \dots, x_k]^k$ and probability $pr \in (0, 1]$, where each location has countably many outgoing transitions and their probabilities sum to $1$. It is *affine* if every $f$ is affine. A *loop* has two locations $q_0, q_1$: one transition from $q_0$ to $q_1$ and only self-loops at $q_1$. In a *guarded* program each transition also carries an equality or inequality predicate on $\vec{x}$; every configuration must have an enabled outgoing transition, and the probabilities of the enabled transitions must sum to $1$. Execution starts in $(q_0, \vec{0})$.

**Moments.** Let $\mathcal{S}^n_q$ be the set of valuations reachable at $q$ after exactly $n$ transitions and $\mathbb{P}(\vec{x} \mid \mathcal{S}^n_q)$ the probability of being in configuration $(q, \vec{x})$ after $n$ transitions (defined inductively by summing over incoming transitions). For a monomial $M$ in the program variables,

$$
\mathbb{E}[M_n] = \sum_{q \in Q} \sum_{\vec{x} \in \mathcal{S}^n_q} M(\vec{x}) \, \mathbb{P}(\vec{x} \mid \mathcal{S}^n_q).
$$

For a positive integer $\ell$ let $\mathbb{E}^{\le \ell} = \{ \mathbb{E}[x_1^{\alpha_1} \cdots x_k^{\alpha_k}] : \alpha_1 + \dots + \alpha_k \le \ell \}$, a finite set of formal variables.

**Definition (Müllner, Moosbrugger and Kovács).** Writing $\mathbb{E}^{\le \ell} = \{ \mathbb{E}[M^{(1)}], \dots, \mathbb{E}[M^{(m)}] \}$, the *moment invariant ideal* of order $\ell$ is

$$
\mathbb{I}^{\le \ell} = \Bigl\{ p \in \overline{\mathbb{Q}}\bigl[\mathbb{E}^{\le \ell}\bigr] \;:\; p\bigl(\mathbb{E}[M^{(1)}_n], \dots, \mathbb{E}[M^{(m)}_n]\bigr) = 0 \text{ for all } n \in \mathbb{N}_0 \Bigr\}.
$$

Its elements are the *polynomial moment invariants* of the loop. It is an ideal of the polynomial ring $\overline{\mathbb{Q}}[\mathbb{E}^{\le \ell}]$, so by Hilbert's basis theorem it has a finite basis; computing a basis means computing the strongest polynomial invariant over the moments of order at most $\ell$.

## Depends on

None.

## Proof depends on

None.

## Expansion

For a non-probabilistic loop the analogue is the invariant ideal, the set of polynomials vanishing on every reachable valuation; the paper shows that moment invariants generalize it, since replacing each probabilistic transition by a nondeterministic one relates the two notions. Ideal membership is decidable from a basis via Gröbner bases, so an algorithm computing bases would decide whether a given polynomial is a moment invariant.

## Sources

- Julian Müllner, Marcel Moosbrugger and Laura Kovács, "Strong Invariants Are Hard: On the Hardness of Strongest Polynomial Invariants for (Probabilistic) Programs", Proceedings of the ACM on Programming Languages 8(POPL), pp. 882–910, 2024, <https://doi.org/10.1145/3632872>; Section 2.1 (program models), Definitions 5.1 and 5.2 and Lemma 5.5 of arXiv:2307.10902v2, <https://arxiv.org/abs/2307.10902v2>.
