# Satisfaction of PDL formulas

Truth of a formula at a world $w$ of a model $M$ is defined
by recursion: an atom $p$ holds at $w$ iff the valuation of $M$ makes $p$ true at $w$; $\bot$
holds nowhere; $\varphi \to \psi$ holds at $w$ iff $\psi$ holds at $w$ whenever $\varphi$ does;
and $[\alpha]\varphi$ holds at $w$ iff $\varphi$ holds at every world $v$ with
$(w, v) \in R_\alpha$, where $R_\alpha$ is the relation denoted by $\alpha$ in $M$.
