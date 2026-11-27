# Target-collision advantage as a collision advantage

Let $X$ and $Y$ have decidable equality. For every keyed hash function $H$ with inputs in $X$ and outputs in $Y$ and every target-collision adversary $A$,

$$
\mathrm{tcrAdv}(H, A) = \mathrm{collAdv}(H, A'),
$$

where $A'$ is the [collision finder obtained from $A$](tcr-to-coll.md): it has the same coins and, on key $s$ and coins $r$, outputs the committed target of $A$ at $r$ and the second message of $A$ at $(s, r)$. The two experiments are literally the same.

This per-adversary equality is not, by itself, an implication between security notions for arbitrary admissible classes. The asymptotic statement that [collision resistance implies target collision resistance](of-collision-resistant.md) also requires that the reduction $A \mapsto A'$ maps admissible target-collision adversaries to admissible collision finders (Katz and Lindell, Section 5.1).
