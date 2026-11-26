# Resource algebras

A *resource algebra* (RA) is a tuple $(M, \mathcal{V}, |\cdot|, \cdot)$ of a set $M$, a validity predicate $\mathcal{V} \subseteq M$, a partial core function $|\cdot| : M \to M^?$ where $M^? = M \uplus \{\bot\}$, and a total composition $\cdot : M \times M \to M$, such that for all $a, b, c$:

- $(a \cdot b) \cdot c = a \cdot (b \cdot c)$ and $a \cdot b = b \cdot a$;
- if $|a| \in M$ then $|a| \cdot a = a$ and $||a|| = |a|$;
- if $|a| \in M$ and $a \preccurlyeq b$ then $|b| \in M$ and $|a| \preccurlyeq |b|$;
- $\mathcal{V}(a \cdot b)$ implies $\mathcal{V}(a)$;

where the extension order is $a \preccurlyeq b \iff \exists c \in M.\ b = a \cdot c$, and composition is lifted to $M^?$ by $a^? \cdot \bot = \bot \cdot a^? = a^?$. A *unital* RA has an element $\varepsilon$ with $\mathcal{V}(\varepsilon)$, $\varepsilon \cdot a = a$ for all $a$, and $|\varepsilon| = \varepsilon$. Every partial commutative monoid gives an RA, with the undefined compositions mapped to an invalid element; RAs use validity instead of partiality to rule out combinations of ownership, and a duplicable core instead of a single unit.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151>, Section 2.1 and Figure 3.
