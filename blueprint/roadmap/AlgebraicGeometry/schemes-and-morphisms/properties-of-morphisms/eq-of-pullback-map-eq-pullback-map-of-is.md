# Equality of morphisms into a separated scheme is detected after field extension

Let $k \to K$ be an extension of fields, let $X$ and $Y$ be schemes over $\operatorname{Spec} k$ with structure morphisms $f_X$ and $f_Y$, and assume $f_Y$ is separated. Let $g_1, g_2 : X \to Y$ be morphisms over $\operatorname{Spec} k$, that is, $f_Y \circ g_1 = f_X$ and $f_Y \circ g_2 = f_X$. If the base-changed morphisms

$$
g_1 \times \mathrm{id},\ g_2 \times \mathrm{id} \;:\; X \times_{\operatorname{Spec} k} \operatorname{Spec} K \longrightarrow Y \times_{\operatorname{Spec} k} \operatorname{Spec} K
$$

are equal, then $g_1 = g_2$.

The first projection $X \times_{\operatorname{Spec} k} \operatorname{Spec} K \to X$ is scheme-theoretically dominant because $k \to K$ is injective, so the equalizer of $g_1$ and $g_2$, a closed immersion by separatedness, has trivial ideal sheaf and is an isomorphism.
