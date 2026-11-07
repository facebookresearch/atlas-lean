# Satisfaction in an epistemic model

Satisfaction of an epistemic formula at a world $w$
of a model $M$ is defined by recursion on the formula, writing $R_i$ for the accessibility
relation of agent $i$ in $M$ and $K_i \varphi$ for the formula "agent $i$ knows $\varphi$": an
atom $a$ holds at $w$ when the valuation of $M$ makes $a$ true at $w$; $\bot$ holds at no world;
$\varphi \to \psi$ holds at $w$ when $\psi$ holds at $w$ whenever $\varphi$ does; and
$K_i \varphi$ holds at $w$ when $\varphi$ holds at every world $v$ with $w \mathrel{R_i} v$.
