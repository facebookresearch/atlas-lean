# q-SDH game

The fixed-generator q-SDH experiment: sample the secret `x`
uniformly from the units `(ZMod q)ˣ` and run the win experiment, sampling the
adversary's coins via `PMF.bind`.

Fixed generators: the experiment of Boneh and Boyen also samples the generators
`g1` and `g2`; this game, like the file's BDH and DDH games, uses the
interface's fixed generators. At prime order `p` the units are the nonzero
residues, so `x` is uniform in `Z_p^×`, as in the source.

Composite-order extension: the source states the experiment at prime order
only. At composite `q` this game keeps the input tuple and the pairing check
and samples `x` from the units of `ZMod q`, the analogue of `Z_p^×`; the check
then rejects every `c` with `x + c` a nonunit, `c = -x` included.

## Sources

- D. Boneh and X. Boyen, *Short Signatures Without Random Oracles and the SDH Assumption in Bilinear Groups*, J. Cryptology 21 (2008), §3.1.
