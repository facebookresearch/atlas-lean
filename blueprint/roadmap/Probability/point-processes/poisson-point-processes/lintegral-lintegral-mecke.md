# Mecke equation

Let $\mu$ be a finite measure on a measurable space $E$, let $\eta$ be distributed as the
[Poisson point process](poisson-point-process.md) with intensity $\mu$, and let
$h : E \times \mathbf{M}(E) \to [0, \infty]$ be jointly measurable, where $\mathbf{M}(E)$ is the
space of measures on $E$. Then

$$\mathbb{E}\Big[\int h(x, \eta)\, \eta(dx)\Big] = \int \mathbb{E}\big[h(x, \eta + \delta_x)\big]\, \mu(dx).$$

## Sources

- J. Mecke, *Stationäre zufällige Maße auf lokalkompakten Abelschen Gruppen*, Zeitschrift für
  Wahrscheinlichkeitstheorie und verwandte Gebiete 9 (1967), 36–58.
- G. Last and M. Penrose, *Lectures on the Poisson Process*, IMS Textbooks, Cambridge University
  Press, 2017, Theorem 4.1.
