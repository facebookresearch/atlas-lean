# Gibbs Factorization

A weight `p` on configurations **factorizes over the cliques** of `G` (Gibbs
factorization): `p` is a finite product of nonnegative potentials `ψ C`, one for each
clique `C` of `G`, where `ψ C` depends only on the variables in `C`. The weight is
unnormalized: the Gibbs normalizing constant `1 / Z` is absorbed into `p`, which does
not change any `CondIndep` statement proved from the factorization below. The family
may include the empty clique; its potential is constant and carries global constants
such as `1 / Z` (see `GibbsFactorization.const_mul`).
