# Fuel-bounded Gotoh recursion

Fix an integer-valued scoring function $\sigma$ on pairs of
letters and integer gap-open and gap-extend penalties $g_o$ and $g_e$. A gap state records what
the previous alignment column was: a match ($\mathrm{none}$), a gap in the second sequence
($\mathrm{gapX}$) or a gap in the first sequence ($\mathrm{gapY}$). For gap states $p$, $q$ let
$c(p, q)$ be the gap cost, $g_e$ if $p = q$ and $g_o$ otherwise. Write $\varepsilon$ for the
empty sequence and $a \cdot u$ for the sequence with first letter $a$ followed by $u$. For fuel
$n \in \mathbb{N}$, sequences $u$, $v$ and a gap state $p$, the integer $G_n(u, v, p)$ is defined
by recursion on $n$: $G_0(u, v, p) = 0$, $G_{n+1}(\varepsilon, \varepsilon, p) = 0$,
$G_{n+1}(\varepsilon, b \cdot v, p) = c(p, \mathrm{gapY}) + G_n(\varepsilon, v, \mathrm{gapY})$,
$G_{n+1}(a \cdot u, \varepsilon, p) = c(p, \mathrm{gapX}) + G_n(u, \varepsilon, \mathrm{gapX})$,
and $G_{n+1}(a \cdot u, b \cdot v, p)$ is the maximum of $\sigma(a, b) + G_n(u, v, \mathrm{none})$,
$c(p, \mathrm{gapX}) + G_n(u, b \cdot v, \mathrm{gapX})$ and
$c(p, \mathrm{gapY}) + G_n(a \cdot u, v, \mathrm{gapY})$.

With fuel at least the sum of the two lengths this is the Gotoh dynamic program; with less fuel
the base case $G_0 = 0$ cuts the recursion short.
