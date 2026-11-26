# Relabelling the letters of an ω-word

Let $v$ be a valuation of atoms on letters of an
alphabet $\Sigma$, let $f \colon \Sigma' \to \Sigma$ be a map, and let $w$ be an ω-word over
$\Sigma'$. For every LTL formula $\varphi$, the relabelled word $i \mapsto f(w(i))$ satisfies
$\varphi$ under $v$ if and only if $w$ satisfies $\varphi$ under the valuation that makes an atom
$a$ true at a letter $s$ of $\Sigma'$ exactly when $v$ makes $a$ true at $f(s)$.

For example, take Boolean valuations as letters, the alphabet of sets of atoms with membership as the valuation, and $f(v) = \{a : v(a) = \mathrm{true}\}$: a Boolean word satisfies $\varphi$, an atom holding where it is true, exactly when its word of set views satisfies $\varphi$.
