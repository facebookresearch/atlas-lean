# Girard's reducibility candidates

In System F, a *reducibility candidate* of type $U$ is a set $\mathcal{R}$ of terms of type $U$ such that

- (CR 1) every $t \in \mathcal{R}$ is strongly normalisable;
- (CR 2) if $t \in \mathcal{R}$ and $t \rightsquigarrow t'$ then $t' \in \mathcal{R}$;
- (CR 3) if $t$ is neutral and every term obtained from $t$ by converting one redex is in $\mathcal{R}$, then $t \in \mathcal{R}$.

In particular every neutral normal term of type $U$ lies in $\mathcal{R}$, so a candidate is never empty, and the strongly normalisable terms of type $U$ form a candidate. For candidates $\mathcal{R}$, $\mathcal{S}$ of types $U$, $V$, the set $\mathcal{R} \to \mathcal{S}$ of terms $t$ of type $U \to V$ with $t\,u \in \mathcal{S}$ for all $u \in \mathcal{R}$ is a candidate of type $U \to V$. For a type $T[\vec X]$, types $\vec U$ and candidates $\vec{\mathcal{R}}$ of these types, *parametric reducibility* $\mathrm{RED}_T[\vec{\mathcal{R}}/\vec X]$, a set of terms of type $T[\vec U/\vec X]$, is defined by $\mathrm{RED}_{X_i}[\vec{\mathcal{R}}/\vec X] = \mathcal{R}_i$, $\mathrm{RED}_{V \to W}[\vec{\mathcal{R}}/\vec X] = \mathrm{RED}_V[\vec{\mathcal{R}}/\vec X] \to \mathrm{RED}_W[\vec{\mathcal{R}}/\vec X]$, and, for $T = \Pi Y.\, W$, as the set of terms $t$ of type $T[\vec U/\vec X]$ such that $t\,V \in \mathrm{RED}_W[\vec{\mathcal{R}}/\vec X, \mathcal{S}/Y]$ for every type $V$ and every candidate $\mathcal{S}$ of type $V$. Then:

1. $\mathrm{RED}_T[\vec{\mathcal{R}}/\vec X]$ is a reducibility candidate of type $T[\vec U/\vec X]$;
2. (substitution) $\mathrm{RED}_{T[V/Y]}[\vec{\mathcal{R}}/\vec X] = \mathrm{RED}_T[\vec{\mathcal{R}}/\vec X, \mathrm{RED}_V[\vec{\mathcal{R}}/\vec X]/Y]$;
3. (universal abstraction) if $w[V/Y] \in \mathrm{RED}_W[\vec{\mathcal{R}}/\vec X, \mathcal{S}/Y]$ for every type $V$ and candidate $\mathcal{S}$ of type $V$, then $\Lambda Y.\, w \in \mathrm{RED}_{\Pi Y.\, W}[\vec{\mathcal{R}}/\vec X]$;
4. (universal application) if $t \in \mathrm{RED}_{\Pi Y.\, W}[\vec{\mathcal{R}}/\vec X]$, then $t\,V \in \mathrm{RED}_{W[V/Y]}[\vec{\mathcal{R}}/\vec X]$ for every type $V$.

## Depends on

- [System F in Church style](system-f-in-church-style.md)

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Sections 14.1.3 and 14.2 (including 14.2.1–14.2.3)
