# De Bruijn terms as locally nameless terms

`toLocallyNameless names t` translates `t` in
the naming context `names`, whose head is the innermost free name: the index `j` becomes
`fvar names[j]` when `j < names.length`.
