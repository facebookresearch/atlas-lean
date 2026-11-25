# Rescaling the concentration unit leaves the response unchanged

For a half-saturation concentration `K > 0`, a Hill coefficient `h > 0`, a concentration `C ≥ 0`, a
factor `s > 0` and every baseline `E0` and maximal increment `Emax`, scaling the half-saturation
concentration and the concentration together does not change the [response](response.md):
`E0 + Emax * (s * C) ^ h / ((s * K) ^ h + (s * C) ^ h)` equals
`E0 + Emax * C ^ h / (K ^ h + C ^ h)`.
