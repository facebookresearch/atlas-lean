# Index of a dart relative to an oriented quotient edge

The indicator of the dart
lying over `q` minus the indicator of its reverse lying over `q`. It is `1` if the dart lies
over `q` and its reverse does not, `-1` if the reverse does and the dart does not, and `0`
otherwise. In particular it is `0` on both darts of an edge that some element of `G` inverts:
the dart and its reverse then lie in one orbit, and the two indicators cancel
(`dartIndex_eq_zero_of_smul_eq_symm`).
