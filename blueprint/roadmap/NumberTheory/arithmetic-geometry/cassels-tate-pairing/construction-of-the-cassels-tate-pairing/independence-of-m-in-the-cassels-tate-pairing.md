# The Cassels–Tate pairing does not depend on m

Let $K$, $A$, $A^\vee$, $a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$ be as in
[The cochains of the Cassels–Tate construction are cocycles](cocycle-conditions-in-the-cassels-tate-construction.md). If $m$
kills $a$ and $a'$ and $n \ge 1$, the sums $\sum_v \mathrm{inv}_v(\bar c_v)$ for Cassels–Tate data for $(a, a', m)$ and for
$(a, a', mn)$ agree. So the value of the construction of [the Cassels–Tate pairing](cassels-tate-pairing-of-an-abelian-variety.md)
does not depend on $m$.

Proof. Take choices $\tau$, $\tau'$, $\sigma$, $\bar\varepsilon$, $\beta_v$, $Q_v$ for $m$. Regard $\tau$ and $\tau'$ as
cocycles with values in $A[mn] \supseteq A[m]$ and $A^\vee[mn] \supseteq A^\vee[m]$, choose a continuous cochain $\sigma^\sharp$
with values in $A[m^2n^2]$ and $n\sigma^\sharp = \sigma$, so that $mn\sigma^\sharp = \tau$, and, at each place, $Q_v^\sharp$ with
$nQ_v^\sharp = Q_v$, so that $mnQ_v^\sharp = \beta_v$, and $\rho_v^\sharp = dQ_v^\sharp$. As $d\sigma^\sharp$ and
$\sigma_v^\sharp - \rho_v^\sharp$ take values in $A[mn]$ and $\tau'$ in $A^\vee[m]$, the relation $e_{mn}(x, x') = e_m(nx, x')$
gives $d\sigma^\sharp \vee_{mn} \tau' = d\sigma \vee_m \tau'$, so that $\bar\varepsilon$ serves again, and
$(\sigma_v^\sharp - \rho_v^\sharp) \vee_{mn} \tau'_v = (\sigma_v - \rho_v) \vee_m \tau'_v$. So the cocycles $\bar\gamma_v$ for $mn$ and
these choices are those for $m$, and the value for $mn$ does not depend on the choices.

## Depends on

- [The cochains of the Cassels–Tate construction are cocycles](cocycle-conditions-in-the-cassels-tate-construction.md), for the Cassels–Tate data

## Proof depends on

- [The Weil pairing is biadditive, Galois-equivariant and compatible in m](bilinearity-of-the-weil-pairing.md), for $e_{mn}(x, x') = e_m(nx, x')$ (its item 3)
- [The Cassels–Tate pairing does not depend on the choices](independence-of-the-choices-in-the-cassels-tate-pairing.md), for the value for $mn$ computed with these choices

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.2, p. 1144 ("One checks that the value is well-defined, and unchanged if $m$ is
  replaced by a prime-to-$p$ multiple").
