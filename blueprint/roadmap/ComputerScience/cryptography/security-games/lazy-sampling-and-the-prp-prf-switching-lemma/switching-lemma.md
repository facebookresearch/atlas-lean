# The PRP/PRF switching lemma

**The PRP/PRF switching lemma** (adaptive, query-bounded). Let `D` be a finite type and `c` an
adaptive distinguisher with oracle access to a function `D → D`, making at most `q` queries along
every path. Its advantage in distinguishing a uniformly random function `f : D → D` from a
uniformly random permutation `π` of `D`, each sampled once and then queried, is at most the
birthday collision probability `Birthday.collisionProb D q = 1 - N (N - 1) ⋯ (N - q + 1) / N ^ q`
with `N = |D|` (Katz and Lindell, Section 3.5.1, the step behind Proposition 3.27; Bellare and
Rogaway, Lemma 1).
