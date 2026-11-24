# Task claim: the Gamma function at r + 1/2 and at 1/2 - r

This temporary note opens the draft pull request that claims the ATLAS task
`af_433148dcc2a4a50c86e40653`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Analysis/sequences-and-series/trigonometric-and-harmonic-series/series-from-n-rlund-s-digamma-identity/gamma-add-half-and-gamma-half-sub-nat.md`
- Lean declaration: `MetaMathlibExt.Gamma_add_half_and_Gamma_half_sub_nat`, a `theorem_wanted` in
  `WantedExt/Analysis/NorlundSeriesWanted.lean`
- Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
  Nörlund*, INTEGERS 25 (2025), Article A18, Lemma 2.

Statement to prove, with its name and statement unchanged: for every complex number $r$ that is
not a negative integer,

$$\Gamma\bigl(r + \tfrac12\bigr) =
\frac{\sqrt{\pi}}{2^{2r}} \cdot \frac{\Gamma(2r + 1)}{\Gamma(r + 1)},$$

where $2^{2r} = e^{2r \log 2}$; and for every natural number $r$,

$$\Gamma\bigl(\tfrac12 - r\bigr) = \frac{(-1)^r \, 2^{2r} \sqrt{\pi}}{r! \binom{2r}{r}}.$$
