# Order of update deliveries

In an event list, each receipt of an update must be
preceded at the same replica by the issue or delivery of each update in its causal history.
The causal history is given by the transitive closure of `DirectlyBefore`. A receipt delivers
an update only if it names a position holding an issue. This predicate checks delivery order
alone; it does not require receipts to refer to earlier positions.
