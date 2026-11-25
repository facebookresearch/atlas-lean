# Of free isos

A sheaf of modules presented by free sheaves over a cover is locally
free. Each chart contributes the tautological generators transported along
its iso via Mathlib's `GeneratingSections.equivOfIso`; the resulting
local generator data is shrunk into the site universe by
`LocalGeneratorsData.isLocallyFree`.
