# Strategy selection on isothermal graphs

Let $G$ be a connected isothermal graph on $N$ vertices with effective degree $\tilde{\kappa} > 1$,
and consider a two-strategy matrix game in which $A$ against $A$ pays $a$, $A$ against $B$ pays $b$,
$B$ against $A$ pays $c$ and $B$ against $B$ pays $d$, with payoffs accumulated from neighbours in
proportion to edge weights and fitness depending on payoff with vanishing selection strength. Under
**death-Birth** updating (a vertex is chosen uniformly to die and a neighbour fills the vacancy with
probability proportional to its edge weight times its fecundity), and equally under **birth-Death**
updating, strategy $A$ is favoured under weak selection if and only if

$$\sigma a + b \ >\ c + \sigma d, \qquad
\sigma = \frac{\tilde{\kappa} + 1 - 4\tilde{\kappa}/N}{\tilde{\kappa} - 1}.$$

Writing $C = -\tfrac12 (a + b - c - d)$ for the cost of playing $A$ and
$B_{\mathrm{en}} = \tfrac12 (a - b + c - d)$ for the benefit it confers on the partner, this
condition is equivalent to

$$\bigl(N/\tilde{\kappa} - 2\bigr)\, B_{\mathrm{en}} \ >\ (N - 2)\, C,$$

so for $B_{\mathrm{en}}, C > 0$ and $\tilde{\kappa} \ll N$ cooperation is favoured exactly when
$B_{\mathrm{en}}/C > \tilde{\kappa}$, while for $\tilde{\kappa} \ge N/2$ cooperation is never
favoured. Under **Birth-death** or **Death-birth** updating the condition is instead
$\sigma a + b > c + \sigma d$ with $\sigma = (N-2)/N$, the well-mixed value; rewritten as
$-(N-1)C - B_{\mathrm{en}} > 0$ it shows that cooperation is never favoured for
$B_{\mathrm{en}}, C > 0$, whatever the isothermal structure.

## Depends on

- [Simpson degree and effective degree of an isothermal graph](simpson-degree-and-effective-degree.md)

## Remarks

An isothermal graph of effective degree $\tilde{\kappa}$ behaves, for weak-selection strategy
selection, exactly like an unweighted $\tilde{\kappa}$-regular graph: substituting $k$ for
$\tilde{\kappa}$ recovers the classical $b/c > k$ rule. The contrast between the two pairs of
update rules reflects the scale of competition: under Birth-death and Death-birth a type competes
with its one-step neighbours, so the benefits it gives away are exactly cancelled; under
death-Birth and birth-Death competition is with two-step neighbours, leaving room for assortment to
pay.

## Sources

- B. Allen, G. Lippner, M. A. Nowak, "Evolutionary games on isothermal graphs",
  Nature Communications 10 (2019) 5107, Eqs. (4), (5), (9) and (10),
  <https://doi.org/10.1038/s41467-019-13006-7> (PMC6841731).
