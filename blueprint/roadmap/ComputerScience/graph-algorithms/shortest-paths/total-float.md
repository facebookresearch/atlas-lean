# Total float of an activity

For a project network `tail head : E → V` with arc durations
`d`, source `s` and sink `t`, the total float of the arc `e` is the latest start of its head
event minus the earliest start of its tail event minus its duration,
`TF(e) = LS(head e) - ES(tail e) - d e`.
