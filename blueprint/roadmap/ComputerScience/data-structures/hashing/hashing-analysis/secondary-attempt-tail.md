# Tail of secondary-hash sampling

For a nonempty finite set of $k$ keys, draw from a
finite indexed family of hashes into $2k^2$ slots. If $q$ is the fraction of family indices whose
hash is not injective on the keys, the chance of still needing a draw after $t$ independent
uniform draws with replacement is $q^t$. The fraction is computed in the rationals (with Lean's
zero denominator convention if given an empty index set, which is not a sampling distribution).
For an empty key set the procedure makes no draws and the tail is zero for every $t$, including
$t=0$; no secondary hash is needed for that branch.
