# Semantic evaluation of kinded type operators

Let $M = (\mathrm{arr}, \mathrm{all})$ be a [kind algebra](kind-algebra.md) on a set $X$. The
evaluation $[\![A]\!]_\eta \in [\![\kappa]\!]_X$ of a [type
operator](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$ in a [semantic environment](kenv.md) $\eta$ for $\Delta$ is defined
by:

- $[\![\alpha_i]\!]_\eta = \eta(\alpha_i)$;
- $[\![\lambda B]\!]_\eta$ is the function $a \mapsto [\![B]\!]_{a \cdot \eta}$;
- $[\![F\,A]\!]_\eta = [\![F]\!]_\eta\,([\![A]\!]_\eta)$;
- $[\![A \to B]\!]_\eta = \mathrm{arr}([\![A]\!]_\eta, [\![B]\!]_\eta)$;
- $[\![\forall_\kappa B]\!]_\eta = \mathrm{all}_\kappa(a \mapsto [\![B]\!]_{a \cdot \eta})$,

where $a \cdot \eta$ is the [extended environment](extend.md). Operator abstraction and application
are interpreted by function abstraction and application.
