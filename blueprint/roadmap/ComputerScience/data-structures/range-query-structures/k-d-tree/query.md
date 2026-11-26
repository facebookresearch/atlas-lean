# Querying a planar rank index

For an index built by `preprocess` from points in
general position, four binary searches count the keys strictly below each lower endpoint and
weakly below each upper endpoint. The intervening ranks form a closed integer box, and each
reported leaf decodes to its original point by x rank.

On any index, an empty computed rank interval yields no points. Otherwise the query reports
in the rank tree and looks up the hits in the x dictionary, skipping out-of-bounds lookups.
Unsorted dictionaries need not give endpoint counts, and inconsistent ranks need not decode
to the intended points. Work charges probes and terminal calls, one setup unit, visited tree
constructors, and one lookup per reported rank point.
