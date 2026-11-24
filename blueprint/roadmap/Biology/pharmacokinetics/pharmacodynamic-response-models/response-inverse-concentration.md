# The inverse concentration attains the prescribed response

For a half-saturation concentration `K > 0`, a Hill coefficient `h > 0`, a maximal increment
`Emax > 0` and a response value strictly between the baseline and the baseline plus the increment,
`E0 < E < E0 + Emax`, the [response](response.md) at the
[inverse concentration](inverse-concentration.md) `C = K * ((E - E0) / (E0 + Emax - E)) ^ (1 / h)`
is `E`: `E0 + Emax * C ^ h / (K ^ h + C ^ h) = E`.
