# Edge Descriptor

An edge descriptor of the SR graph: species `s`, reaction node `r`, and the side whose
complex would label the edge. Every triple is a descriptor; it describes an actual edge of the SR
graph of a network only when `s` occurs in that complex (`SRNetwork.IsEdge`).
