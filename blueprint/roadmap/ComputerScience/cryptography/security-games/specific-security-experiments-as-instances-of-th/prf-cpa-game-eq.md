# Up-front and fresh randomness give the same CPA experiment

For `F : K → X → Y` and a CPA adversary `A` making at most `q` encryption
queries over both stages, the CPA experiment of `F` with the encryption
randomness drawn up front as `ρ : Fin q → X` equals the CPA experiment
`PrivK^cpa` of `prfEnc F`, which draws fresh randomness per query, for the
adversary with uniform coins (Katz and Lindell, Construction 3.30 and
Definition 3.22). Without the query bound the two experiments differ: the
up-front version stops an adversary at its `(q + 1)`-st query and outputs the
guess `false`.
