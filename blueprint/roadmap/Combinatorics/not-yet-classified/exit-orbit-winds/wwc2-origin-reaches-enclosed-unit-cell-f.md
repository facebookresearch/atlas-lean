# Wwc2 origin Reaches Enclosed unit Cell false

The reaches-enclosed property fails for the unit-cell loop: the origin is enclosed by it
(`wwc2_unitCell_originInside`) and lies on it (it is the loop's starting face), so no walk from
the origin to the origin can avoid the loop's support. This refutes, at the unit-cell instance,
the universal premise that the removed `wwc2_pc_lt_one_of_originReachesEnclosed` would have
needed: for the all-closed configuration the origin cluster is the singleton `unitCell`, and the
exit loop is this unit-cell loop.
