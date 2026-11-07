# Satisfaction in a Kripke model

Let $M$ be a Kripke model with accessibility relation
$R$. Satisfaction of a modal formula at a world $w$ of $M$ is defined by recursion on the
formula: $w$ satisfies an atom $p$ if and only if the valuation of $M$ makes $p$ true at $w$;
$w$ never satisfies $\bot$; $w$ satisfies $\varphi \to \psi$ if and only if $w$ satisfies
$\psi$ whenever it satisfies $\varphi$; and $w$ satisfies $\Box\varphi$ if and only if every
world $v$ with $w \mathrel{R} v$ satisfies $\varphi$.
