# Duality

Let $M$ be a Kripke model, $\rho$ an environment assigning a set of worlds to
each variable index $n \in \mathbb{N}$, and $\varphi$ a μ-calculus formula. Let $\neg\varphi$ be
the dual formula of $\varphi$, obtained by swapping atoms with negated atoms, $\bot$ with $\top$,
$\wedge$ with $\vee$, $\Box$ with $\Diamond$ and $\mu$ with $\nu$, and keeping variables. Write
$\overline{\rho}$ for the environment sending each index $n$ to the complement of $\rho(n)$. Then
for every world $w$, $w$ satisfies $\neg\varphi$ in $M$ under $\overline{\rho}$ if and only if $w$
does not satisfy $\varphi$ in $M$ under $\rho$.
