# Potts model of a protein family and context-dependent mutational effects

Let sequences $(a_1, \dots, a_L)$ of length $L$ take values in an alphabet of $q$ symbols (the 20
amino acids and a gap). The **independent-site (profile) model** assigns

$$P_{\mathrm{IND}}(a_1,\dots,a_L) = \prod_{i=1}^{L} f_i(a_i), \qquad
\phi_{\mathrm{IND}}(a_1,\dots,a_L) = \log P_{\mathrm{IND}} = \sum_{i=1}^{L} \varphi_i(a_i),$$

with $\varphi_i(a) = \log f_i(a)$ and $f_i(a)$ the (regularized) frequency of symbol $a$ in column
$i$ of the alignment. The **pairwise (Potts) model** is

$$P_{\mathrm{DCA}}(a_1,\dots,a_L) = \frac{1}{Z}\exp\{\phi_{\mathrm{DCA}}(a_1,\dots,a_L)\}, \qquad
\phi_{\mathrm{DCA}} = \sum_{i=1}^{L}\varphi_i(a_i) + \sum_{1 \le i < j \le L}\varphi_{ij}(a_i, a_j),$$

where $Z = \sum_{a_1,\dots,a_L} \exp\{\phi_{\mathrm{DCA}}\}$, the fields $\varphi_i$ act on single
sites and the couplings $\varphi_{ij}$, defined for pairs of distinct sites and extended by
$\varphi_{ji}(b, a) = \varphi_{ij}(a, b)$ for $i < j$, encode pairwise epistasis; setting all
couplings to zero recovers the profile model. The predicted effect of the substitution $a_i \to b$ in a wild-type
sequence is the log-probability difference

$$\Delta\phi_{\mathrm{DCA}}(a_i \to b \mid a_{\setminus i}) = \varphi_i(b) - \varphi_i(a_i)
+ \sum_{j \ne i}\big[\varphi_{ij}(b, a_j) - \varphi_{ij}(a_i, a_j)\big],$$

which depends on every other residue $a_j$, $j \ne i$, of the background sequence, whereas the
profile score $\varphi_i(b) - \varphi_i(a_i)$ does not.

## Expansion

The partition function cancels in log-probability differences, so mutational scores need only
the fields and couplings. Under the profile model, the effects of mutations at different sites add;
under the Potts model, the same substitution can be favourable in one background and deleterious
in another, because the coupling sum changes with the background. In the source, scores for single
mutants of the TEM-1 beta-lactamase are mapped to antibiotic resistance levels by matching ranks,
and the Potts score correlates better with measured resistance than the profile score or
structure-based stability predictions; the largest couplings also predict tertiary contacts.
The source sums the couplings over $i \le j$ and the mutational score over all $j$; with a
diagonal coupling the $j = i$ term of that score would be
$\varphi_{ii}(b, a_i) - \varphi_{ii}(a_i, a_i)$ instead of the change
$\varphi_{ii}(b, b) - \varphi_{ii}(a_i, a_i)$ of $\phi_{\mathrm{DCA}}$, so the score would not be the
log-probability difference. Here couplings are restricted to distinct sites; a diagonal term is a
function of one site and can be absorbed into the field.

## Sources

- M. Figliuzzi, H. Jacquier, A. Schug, O. Tenaillon, M. Weigt, "Coevolutionary landscape inference
  and the context-dependence of mutations in beta-lactamase TEM-1", Molecular Biology and Evolution
  33 (2016) 268-280, Results (Eqs. 2-4) and Materials and Methods, "Statistical Sequence Modeling"
  (Eqs. 8-11), <https://doi.org/10.1093/molbev/msv211> (PMC4693977).
