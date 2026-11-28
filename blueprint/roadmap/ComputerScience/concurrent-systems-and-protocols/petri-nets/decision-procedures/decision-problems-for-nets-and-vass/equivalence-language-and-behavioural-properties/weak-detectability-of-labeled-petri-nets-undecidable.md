# Weak detectability of labeled Petri nets is undecidable

A discrete-event system is weakly detectable if, along some infinite behavior, an observer eventually always knows the current state from the observations. For systems modeled by unbounded labeled Petri nets this is undecidable, while strong detectability (along every behavior) is decidable.

**Setting (Masopust and Yin).** A Petri net $N = (P, T, \mathit{Pre}, \mathit{Post})$ has finite disjoint sets of places and transitions and arc weights $\mathit{Pre}, \mathit{Post} : P \times T \to \mathbb{N}$; a transition $t$ is enabled at a marking $M$ if $M(p) \ge \mathit{Pre}(p, t)$ for all $p$, and firing it gives $M(p) - \mathit{Pre}(p, t) + \mathit{Post}(p, t)$. A *labeled Petri net system* (LPN) $G = (N, M_0, \Sigma, \ell)$ adds an initial marking, an alphabet $\Sigma$ and a labeling $\ell : T \to \Sigma \cup \{\varepsilon\}$; transitions labeled $\varepsilon$ are unobservable. $L(G)$ and $L^\omega(G)$ are the sets of finite and infinite observations $\ell(\sigma)$ of firing sequences $\sigma$ from $M_0$, and for $s \in L(G)$, $R(G, s)$ is the set of markings reached by firing sequences with observation $s$. As usual for detectability, systems are assumed deadlock free and unable to generate infinite unobservable sequences. $G$ is *weakly detectable* if there are an integer $n \ge 0$ and an infinite observation $s \in L^\omega(G)$ such that $|R(G, s')| = 1$ for every prefix $s'$ of $s$ of length at least $n$; it is *strongly detectable* if there is an $n$ such that this holds for every $s \in L^\omega(G)$.

**Theorem (Masopust and Yin).** Weak detectability is undecidable for labeled Petri nets.

The same paper shows that strong detectability is decidable for labeled Petri nets but EXPSPACE-hard, and that single-marking current-state opacity is undecidable. For finite-state systems weak detectability is PSPACE-complete.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Language and trace equivalence of labeled Petri nets are undecidable](language-and-trace-equivalence-are-undecidable.md)

## Expansion

The proof reduces from language inclusion for labeled Petri nets without unobservable transitions, which is undecidable by Hack (inclusion of trace sets is undecidable because trace equivalence is). From such nets $G_1$ and $G_2$ the authors build a net $G$ that, after an initial $x$, simulates either $G_1$ or $G_2$ and can then emit $x$ again followed by letters $a$ and $b$, so that its infinite observations are $x w x a^{y(w)} b^\omega$ for $w \in L(G_1)$, where $y(w)$ is bounded by the tokens left in $G_1$, $x w x (a^\omega + a^\ast b^\omega)$ for $w \in L(G_2)$, and the infinite observations of $G_1$ and $G_2$ after $x$. The net contains two identical copies of $G_2$, so every observation through the $G_2$ part is consistent with at least two markings; if $L(G_1) \subseteq L(G_2)$, every observation through the $G_1$ part can also be produced through the $G_2$ part, so $G$ is not weakly detectable. If some $w \in L(G_1) \setminus L(G_2)$ exists, let $k$ be the largest total number of tokens of $G_1$ after $w$; the observation $x w x a^k b^\omega$ uses up all tokens of $G_1$ and then stays in a single marking forever. Hence $G$ is weakly detectable exactly when inclusion fails.

## Sources

- Tomáš Masopust and Xiang Yin, "Deciding detectability for labeled Petri nets", Automatica 104, pp. 238–241, 2019, <https://doi.org/10.1016/j.automatica.2019.02.058>; Section 2 (labeled Petri nets and the standing assumptions), the definitions of strong and weak detectability and the weak detectability undecidability theorem of Section 4, read in arXiv:1802.02087v2, <https://arxiv.org/abs/1802.02087v2>.
