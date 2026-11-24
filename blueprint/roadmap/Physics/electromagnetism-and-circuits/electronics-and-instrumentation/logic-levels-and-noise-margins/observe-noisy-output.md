# Observe noisy output

The output-observation contract: if a gate's ideal output voltage
is promised low (`<= Vol`) when its expected output bit is `false` and
high (`>= Voh`) when its expected output bit is `true`, with
`Vol < Vil < Vih < Voh`, then additive noise below both margins makes
the physical observation of the noisy output equal that expected
output bit. No gate function is modeled: the premise `hy` says directly
that the ideal output voltage encodes the expected output bit. Here
the two margins are `Vil - Vol` and `Voh - Vih`.
