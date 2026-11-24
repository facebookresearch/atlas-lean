# Horseshoe Data

Horseshoe-type input data for the long exact sequence of right-derived
functors: injective resolutions of the three terms of a short exact sequence
`S`, with chosen lifts of `S.f` and `S.g` to the resolution complexes, plus a
degreewise splitting of the resulting diagram of complexes.

The middle resolution and the splittings are arbitrary compatible choices.
`HorseshoeData.ofEndpoints` supplies such data from the injective horseshoe
with prescribed endpoint resolutions. Source-specific factories may supply
other compatible middle resolutions without changing this interface.
