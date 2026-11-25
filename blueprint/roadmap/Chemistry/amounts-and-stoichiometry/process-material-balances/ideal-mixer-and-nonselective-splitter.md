# Ideal mixer and nonselective splitter

Let a steady process unit have finite sets of species, inlet streams, and outlet streams. Each stream carries species flows
in $\mathbb{R}^S_{\ge 0}$, where $S$ is the species set. A stream with positive total flow has composition equal to its flow
vector divided by its total.

- **Mixer.** The outlet flow vector of a mixer is the sum of its inlet flow vectors. If the outlet total is positive, its
  composition is the convex combination of the compositions of the inlets with positive flow, weighted by their shares of the
  total flow; inlets with zero flow have no composition and do not contribute.
- **Nonselective splitter.** With split fractions $\phi_k \ge 0$, $\sum_k \phi_k = 1$, outlet $k$ carries $\phi_k$ times the inlet
  flow vector. The outlets add up to the inlet, and every outlet with positive flow has the composition of the inlet.

The unit has no storage and no reaction. Equilibrium stages and other selective separators are not of this form.

## Sources

- *Introduction to Chemical Engineering Processes*, Wikibooks, chapter "How to Analyze a Recycle System" (splitter balances with equal composition of the outlets), <https://en.wikibooks.org/wiki/Introduction_to_Chemical_Engineering_Processes/How_to_Analyze_a_Recycle_System>.
