# Negation of μ-calculus formulas

The meta-level negation $\neg\varphi$ of a μ-calculus
formula $\varphi$ swaps each connective with its dual. It is defined by recursion: an atom $p$
becomes the negated atom $\overline{p}$ and $\overline{p}$ becomes $p$, each variable $x_n$
stays $x_n$, $\neg\bot = \top$, $\neg\top = \bot$,
$\neg(\varphi \wedge \psi) = \neg\varphi \vee \neg\psi$,
$\neg(\varphi \vee \psi) = \neg\varphi \wedge \neg\psi$, $\neg\Box\varphi = \Diamond\neg\varphi$,
$\neg\Diamond\varphi = \Box\neg\varphi$, $\neg\mu\varphi = \nu\neg\varphi$ and
$\neg\nu\varphi = \mu\neg\varphi$.
