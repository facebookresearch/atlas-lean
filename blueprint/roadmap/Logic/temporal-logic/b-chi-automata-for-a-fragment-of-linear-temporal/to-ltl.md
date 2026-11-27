# Propositional formulas as LTL formulas

The translation of propositional formulas into LTL
formulas is defined by recursion: an atom $a$ goes to the LTL atom $a$, truth goes to the LTL
truth constant $\top$, $\neg\varphi$ goes to the LTL negation of the translation of $\varphi$, and
$\varphi \wedge \psi$ goes to the LTL conjunction of the translations of $\varphi$ and $\psi$.
