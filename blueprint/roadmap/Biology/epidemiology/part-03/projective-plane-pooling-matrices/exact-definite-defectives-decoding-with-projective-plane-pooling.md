# Exact definite-defectives decoding with projective-plane pooling matrices

**Setting.** $M$ samples, each infected or not, are assigned to $N$ pools by a binary **pooling matrix** $H\in\{0,1\}^{N\times M}$ ($H_{ij}=1$ if sample $j$ goes into pool $i$); in the noiseless model a pool tests positive iff it contains at least one positive sample. The **definite defectives (DD)** decoder (i) declares negative every sample lying in some negative pool, then (ii) declares positive every sample that is the only not-yet-cleared sample in some positive pool; all other samples are "undecoded". With correct test results DD makes no false positive: step (i) only clears true negatives and step (ii) only flags true positives. The two-stage DD2 protocol retests undecoded samples individually.

**PPoL construction.** Let $m$ be a prime power, $p=m^2+m+1$, and $D_0=\{a_0,\dots,a_m\}\subset\mathbb Z_p$ a perfect difference set (every nonzero residue is a difference $a_i-a_j$ in exactly one way). Its translates $D_\ell=D_0+\ell$ are the lines of a finite projective plane of order $m$ on the points $\mathbb Z_p$. Fix $1\le d_1\le m+1$. Delete the $m+1$ lines through the point $0$; the remaining $m^2$ lines are the samples. Take as pools the points $B$ lying on $d_1$ of the deleted lines (other than $0$). Packing these $d_1$ pencils gives a $d_1m\times m^2$ matrix $H$.

**Proposition (degrees and intersections).** Every sample is in exactly $d_1$ pools and every pool contains exactly $m$ samples. Any two columns (samples) of $H$ share at most one pool, and any two rows (pools) share at most one sample; equivalently the bipartite pool–sample graph has girth at least $6$.

**Theorem (exact decoding).** In the noiseless setting, if the number of positive samples is at most $d_1-1$, the DD decoder correctly classifies every sample with the $d_1m$ pooled tests alone (no second stage).

## Expansion

Each remaining line meets each deleted line through $0$ in exactly one point, which gives the degrees. Two distinct lines of a projective plane meet in exactly one point and two points lie on exactly one line, so two samples share at most one pool and a $4$-cycle would force two lines to share two points. For exact decoding, take a negative sample: its $d_1$ pools could each be made positive only by a distinct positive sample (two samples share at most one pool), and there are at most $d_1-1$ positives, so one of its pools is negative and step (i) clears it. A positive sample has at most $d_1-2$ other positives meeting its $d_1$ pools, so one of its pools contains no other positive; once negatives are cleared it is the only remaining sample there and step (ii) flags it. The relative cost of DD2 with PPoL matrices beats fixed designs (2D pooling, Reed–Solomon designs) only in prevalence bands, so $(m,d_1)$ should be tuned to the prevalence.

## Sources

- Y.-J. Lin, C.-H. Yu, T.-H. Liu and C.-S. Chang, "Constructions and comparisons of pooling matrices for pooled testing of COVID-19", arXiv:2010.00060 (2020), sections on the DD algorithm (proposition citing Aldridge et al., Lemma 2.2) and on perfect difference sets and finite projective planes (PPoL algorithm, propositions on degree and intersection, girth corollary, detection theorem), <https://doi.org/10.48550/arXiv.2010.00060>.
