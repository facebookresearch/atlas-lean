# Attributes of a selection condition

The set of attributes mentioned by a selection
condition, defined by recursion: it is empty for the always-true condition; for the comparison
$a = d$ of an attribute $a$ with a constant $d$ it is $\{a\}$; for the comparison $a = b$ of
attributes $a$ and $b$ it is $\{a, b\}$; for the negation $\neg \varphi$ of a condition $\varphi$
it is the set of attributes of $\varphi$; and for the conjunction $\varphi \land \psi$ of
conditions $\varphi$ and $\psi$ it is the union of the attributes of $\varphi$ and of $\psi$.
