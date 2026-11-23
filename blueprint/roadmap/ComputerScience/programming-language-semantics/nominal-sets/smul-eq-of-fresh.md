# Permutations moving only fresh atoms fix the element

Let $\mathbb{A}$ be an infinite set of atoms and $X$ a set with an action of the group $\mathrm{Perm}_f(\mathbb{A})$ of [finitely supported permutations](fin-perm.md) of $\mathbb{A}$. Let $x \in X$ and let $F$ be a finite set of atoms each of which is [fresh](fresh.md) for $x$. Every finitely supported permutation $\pi$ that fixes every atom outside $F$ fixes $x$.

The proof is by induction on $F$. If $\pi(a) = a$ for the atom $a$ removed from $F$, the induction hypothesis applies to $\pi$; otherwise $\pi = (a\ b)\,\pi'$ with $b = \pi(a)$, where $\pi'$ fixes $a$ and every atom outside $F \setminus \{a\}$, and $(a\ b)$ fixes $x$ since $a$ and $b$ are fresh.
