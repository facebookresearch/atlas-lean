# Kind-indexed candidate semantics for F-omega

In System $F_\omega$, kinds are built from $*$ by $K_1 \to K_2$, and types are built from variables and constants by $\Rightarrow$, $\Pi_K$, abstraction $\lambda t{:}K.\, \sigma$ and
application, subject to kind checking. Fix a kind assignment $\Delta$ to type variables. Girard's candidate semantics assigns to each type
$\sigma$ that kind-checks under $\Delta$ a nonempty set $\mathcal{C}_\sigma$:

- if $\sigma$ has kind $*$, $\mathcal{C}_\sigma$ is a set of sets of provable typing judgments of type $\sigma$, closed under the arrow construction
  $[C \Rightarrow D] \in \mathcal{C}_{\sigma \Rightarrow \tau}$ for $C \in \mathcal{C}_\sigma$, $D \in \mathcal{C}_\tau$, and under the intersections used for $\Pi_K$;
- if $\sigma$ has kind $K_1 \to K_2$, $\mathcal{C}_\sigma$ is a set of functions $f$ sending each pair $(\tau, C)$ of a type $\tau$ of kind $K_1$ and an element $C \in \mathcal{C}_\tau$ to
  an element of $\mathcal{C}_{\sigma\tau}$.

A *candidate assignment* $\langle \theta, \eta \rangle$ gives each type variable $t$ of kind $K$ a type $\theta(t)$ of kind $K$ and an element $\eta(t) \in \mathcal{C}_{\theta(t)}$. The
interpretation is defined by $[\![t]\!]_{\theta\eta} = \eta(t)$, $[\![\sigma \Rightarrow \tau]\!] = [\,[\![\sigma]\!] \Rightarrow [\![\tau]\!]\,]$, $[\![\sigma\tau]\!]_{\theta\eta} = [\![\sigma]\!]_{\theta\eta}(\theta(\tau), [\![\tau]\!]_{\theta\eta})$, abstraction
as the corresponding function, and $[\![\Pi_K \sigma]\!]$ as the set of judgments $M$ with $M\tau \in \bigcap_{C \in \mathcal{C}_\tau} [\![\sigma]\!](\tau, C)$ for every type $\tau$ of kind $K$. Then:

1. (substitution) $[\![\sigma[\tau/t]]\!]_{\theta\eta} = [\![\sigma]\!]_{\theta[t := \theta(\tau)],\, \eta[t := [\![\tau]\!]_{\theta\eta}]}$;
2. (conversion invariance) if $\sigma$ and $\sigma'$ are $\beta\eta$-convertible then $[\![\sigma]\!]_{\theta\eta} = [\![\sigma']\!]_{\theta\eta}$;
3. (Girard) $[\![\sigma]\!]_{\theta\eta} \in \mathcal{C}_{\theta(\sigma)}$.

Conversion invariance follows from the substitution property; it does not require normalizing types first.

## Depends on

- [Girard's reducibility candidates](girard-s-reducibility-candidates.md)

## Sources

- J. Gallier, "On Girard's 'candidats de réductibilité'", in P. Odifreddi (ed.), *Logic and Computer Science*, Academic Press, 1990, <https://www.cis.upenn.edu/~jean/sngirard.pdf>: Sections 12 and 14 (kinds, types and kind checking of $F_\omega$, Definitions 12.1–12.3) and Section 16 (Definitions 16.1–16.4, Lemmas 16.5–16.8, and the families of candidates in Definition 16.9).
- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989: Chapter 14 (the System F case, not $F_\omega$).
