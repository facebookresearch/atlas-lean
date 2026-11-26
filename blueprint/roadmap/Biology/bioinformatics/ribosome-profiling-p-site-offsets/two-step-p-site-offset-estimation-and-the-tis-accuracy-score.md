# Two-step P-site offset estimation and the TIS accuracy score

Consider ribosome-profiling reads that overlap annotated translation initiation sites (TIS), grouped
by read length $L \in [L_{\min}, L_{\max}]$, and a flanking length $\mathrm{FL} \ge 0$ (reads with an
end within $\mathrm{FL}$ nucleotides of the start codon are discarded). For each length bin let
$f_L^{5'}(x)$ and $f_L^{3'}(x)$ be the numbers of read $5'$ and $3'$ ends at position $x$ relative
to the first nucleotide of the start codon.

**Step 1 (temporary offsets).** The temporary offsets $5'\mathrm{tPO}_L$ and $3'\mathrm{tPO}_L$
are the positions of the global maxima

$$f_L^{5'}(-5'\mathrm{tPO}_L) \ge f_L^{5'}(x)\ \ \forall x \in [-L + \mathrm{FL},\, -\mathrm{FL}], \qquad
f_L^{3'}(3'\mathrm{tPO}_L) \ge f_L^{3'}(x)\ \ \forall x \in [\mathrm{FL} - 1,\, L - \mathrm{FL} - 1].$$

Assigning to each of the $N$ TIS-overlapping reads the temporary offsets of its length gives the
read-level multisets $5'\mathrm{tPO}_R$ and $3'\mathrm{tPO}_R$. The optimal offset $\mathrm{oPO}$ is
the more frequent of the two modes, $\operatorname{Mode}(5'\mathrm{tPO}_R)$ and
$\operatorname{Mode}(3'\mathrm{tPO}_R)$ (ties go to the $5'$ end), and that choice fixes the optimal
extremity.

**Step 2 (correction).** For each length $L$ whose offset at the optimal extremity differs from
$\mathrm{oPO}$, let $\mathrm{LMP}_L$ be the set of distances from the TIS of the local maxima of the
occupancy profile at the optimal extremity. The corrected offset is the local maximum closest to
the optimal one,

$$\mathrm{cPO}_L = \operatorname*{arg\,min}_{x \in \mathrm{LMP}_L} |x - \mathrm{oPO}| .$$

**TIS accuracy score.** With $f(x)$ the profile of assigned P-sites relative to the TIS, the score

$$\frac{\sum_{x \in [0, 14],\ 3 \mid x} f(x)}{\sum_{x \in [-15, 14],\ 3 \mid x} f(x)}$$

equals $1$ when in-frame periodicity appears only downstream of the start codon and decreases as
spurious periodicity appears in the $5'$ untranslated region.

## Expansion

The P-site sits at a roughly fixed distance from one end of the protected fragment, but that
distance varies with fragment length because of ribosome conformations and nuclease digestion. A
per-length global maximum is noisy for rare lengths and can be pulled by ribosomes near but not on
the start codon, producing offsets that jump between lengths differing by one nucleotide. The
most abundant read population gives a reliable reference, and choosing for every other length the
local maximum nearest to that reference keeps offsets coherent across lengths while still using
each length's own occupancy profile. Because translating ribosomes advance codon by codon, correctly
placed P-sites show three-nucleotide periodicity inside coding sequences only, which the TIS
accuracy score measures in a 30-nucleotide window around the start codon.

## Sources

- F. Lauria, T. Tebaldi, P. Bernabò, E. J. N. Groen, T. H. Gillingwater, G. Viero, "riboWaltz:
  Optimization of ribosome P-site positioning in ribosome profiling data", PLoS Computational
  Biology 14 (2018) e1006169, Design and implementation (P-site offset computation and correction)
  and Results (TIS accuracy score), <https://doi.org/10.1371/journal.pcbi.1006169> (PMC6112680).
