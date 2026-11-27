# Step

A legal single-heap transition with its primitive work. Insertion charges allocation, splice
and minimum update; find-min reads the cache. Decrease charges three fixed units for the key,
parent-order and cache work and two per cut (splice/unmark and cascade test).
