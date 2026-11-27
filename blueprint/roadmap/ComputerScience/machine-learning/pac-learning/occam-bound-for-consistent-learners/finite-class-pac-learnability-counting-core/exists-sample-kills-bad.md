# A sample that rules out every wrong hypothesis of a finite class

Let $X$ be a finite set, $c : X \to \{0, 1\}$ a target, $C$ a finite class of hypotheses $X \to \{0, 1\}$, and $m \in \mathbb{N}$ with $|C|\,\max(|X| - 1, 0)^m < |X|^m$ (truncated subtraction: for empty $X$ the base is $0$, not $-1$). Then some sample $s \in X^m$ rules out every wrong hypothesis of $C$: every $h \in C$ that agrees with $c$ at all sampled points equals $c$.
