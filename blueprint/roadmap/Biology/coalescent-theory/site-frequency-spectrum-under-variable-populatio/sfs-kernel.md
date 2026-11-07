# Griffiths–Tavaré kernel

The **Griffiths–Tavaré kernel** `k C(n-i-1, k-2) / C(n-1, k-1)`: the expected number of
branches subtending exactly `i` of the `n` sample copies while `k` lineages remain
(`SiteFrequencySpectrum.joinStep_iterate_count`). Meaningful for `1 ≤ i < n`, `2 ≤ k ≤ n`;
outside that range the natural-number subtractions give junk values.
