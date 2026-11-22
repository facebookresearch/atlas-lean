# Chem Pot

Chemical potential of species `i` as a partial derivative of entropy:
`μᵢ = -T * (∂S/∂Nᵢ)`. Physically meaningful on the domain of a
`FundamentalRelation`; elsewhere it inherits the junk values of `temp` and `dSdN`.
