# Operational semantics over a labelled transition system

An operational semantics on configurations `Config` with labels `Label` consists of a labelled transition system on `Config` and a predicate `Final` of final configurations (values), required to be terminal: no final configuration has an outgoing transition. `Final` is part of the data, not defined as terminality, so a terminal configuration that is not final is stuck.
