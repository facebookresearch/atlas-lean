# Root-weight line arrows of a groupified chart are functorial

Let $Y$ be a scheme, $P$ a
commutative monoid, $D$ a Deligne–Faltings chart of $Y$ over $P$ (line bundles $L_p$ with sections
$s_p$ for $p \in P$, compatible with units and tensor products) and $G$ an extension of $D$ to the
groupification $P^{\mathrm{gp}}$ (line bundles $L_v$ for $v \in P^{\mathrm{gp}}$, with unit and
multiplication isomorphisms and identifications $L_{[p]} \cong L_p$). For a weight arrow
$a : v \to w$ labelled by $p \in P$ with $[p]\,v = w$, let $L_v \to L_w$ (`lineArrow G a`) be
tensoring with the section $s_p$, followed by $L_p \cong L_{[p]}$ and the multiplication
$L_{[p]} \otimes L_v \cong L_w$. These arrows send identities to identities and composites to
composites (`LineFunctorLaws G`).
